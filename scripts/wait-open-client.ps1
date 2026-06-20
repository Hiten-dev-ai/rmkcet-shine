param(
  [Parameter(Mandatory = $true)]
  [string]$ClientUrl,

  [string]$ServerUrl = "",

  [int]$TimeoutSeconds = 180
)

$deadline = (Get-Date).AddSeconds([Math]::Max(5, $TimeoutSeconds))

function Test-ShineUrl {
  param([string]$Url)
  if ([string]::IsNullOrWhiteSpace($Url)) {
    return $true
  }
  try {
    $response = Invoke-WebRequest -Uri $Url -UseBasicParsing -TimeoutSec 2
    return ($response.StatusCode -ge 200 -and $response.StatusCode -lt 500)
  } catch {
    return $false
  }
}

while ((Get-Date) -lt $deadline) {
  if ((Test-ShineUrl -Url $ClientUrl) -and (Test-ShineUrl -Url $ServerUrl)) {
    Start-Process $ClientUrl
    exit 0
  }
  Start-Sleep -Seconds 1
}

Start-Process $ClientUrl
